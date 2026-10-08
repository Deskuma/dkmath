# Report 018 - Centered fold gcd and odd-gap aggregate

Instruction 018 is implemented. The exact gcd normal form, odd-prime support,
existing primorial bridge, positive-anchor composite detector, multiplicity
formulas and order-four cyclotomic address are kernel-checked. The two gcd
aggregates are coprime across consecutive shells. No new positive-anchor
full-cover obstruction or primitive first-appearance law is proved.

New prose/checkpoint artifacts use ASCII text without backslash or LaTeX
notation. Exact source names are in
[source-inventory-018.md](source-inventory-018.md); declaration and validation
scope is recorded in [validation-018.md](validation-018.md).

Throughout this report, for j<n:

    L = n^2+n-j; R = n^2+n+1+j; G_j = 2*j+1.
    N_n = centeredFoldNorm n = n^2+(n+1)^2.
    H_n = centeredOddGapProduct n.
    A_n = centeredNormGapGcd n.
    P_n = centeredFoldGcdProduct n.

All of these are natural-number arithmetic objects. A_n is the visible norm
divisor; P_n measures repeated common-divisor multiplicity across seats.

## 1. Exact centered pair gcd normal form

centeredPair_gcd_eq_norm_gap proves exactly:

    gcd(L,R) = gcd(N_n,G_j), for j<n.

The proof rewrites R=L+G_j and N_n=2*L+G_j, then cancels the factor 2 because
G_j is odd and hence coprime to 2. It uses Nat.gcd_self_add_right,
Nat.gcd_add_self_left and Nat.Coprime.gcd_mul_left_cancel. There is no new
valuation proof, unproved factor-cancellation hypothesis or unsafe Nat
subtraction in this step.

Regressions include gap one at every positive anchor; n=3,j=2 with fresh gcd5;
n=6,j=2 with old gcd5; and n=21,j=12 with repeated-prime gcd25. The last is the
first repeated-prime local gcd in the finite ascending-anchor/pair scan.

## 2. Exact old and fresh prime consequences

Every local gcd divides N_n and G_j, is odd, and has all prime divisors 1 mod4.
Every divisor of a local gcd is below 2*n, using the positive internal gap and
its bound G_j<2*n. In particular a fresh prime common divisor has n<p<2*n.

The existing OldSupportGcd classification is preserved: bounded support is
disjoint iff the complete-point gcd is 1 or one fresh prime above n. It is
not equivalent merely to gcd one. centeredPair_oldSupport_disjoint_iff exposes
that classification in the new norm/gap coordinates.

Old/fresh is a classification of prime factors, not just the magnitude of
the gcd. The first bounded counterexample to "gcd>n means a fresh prime" is
n=21,j=12: gcd450,475=25>21, but its prime5 is old and appears in both bounded
supports. The kernel regression large_gcd_with_old_support retains this case.

## 3. Finite object for the odd-gap ladder

centeredOddGapProduct is an abbreviation of Mathlib's existing
Nat.doubleFactorial (2*n-1). No competing generic odd-product definition was
introduced. It is bridged to the shell coordinates by:

    H_n = product over j in range n of (2*j+1).
    H_n = product of centeredInternalGaps n.
    H_0 = 1; H_n>0; H_(n+1)=H_n*(2*n+1).

At n=0, the underlying double factorial is 0 double factorial, equal to 1;
this supplies the required empty product convention without a negative Nat
index. Existing Mathlib doubleFactorial_eq_prod_odd has a shifted index and
starts with the nontrivial factor3; the shell-facing bridge includes factor1.

The Pascal/Wallis central and mirror half-products were audited. They are
rational ratios using oddLeftQ and oddRightQ, rather than a new natural odd
product. Their APIs were retained and no Wallis limit or analytic dependency
was imported into Legendre.

## 4. Exact prime support

prime_dvd_centeredOddGapProduct_iff proves, for prime p:

    p divides H_n iff p!=2 and p<2*n.

The forward direction uses prime divisibility of a finite product and the
gap bound. In the reverse direction an odd prime is literally one gap
p=2*j+1 with j<n. The statement handles n=0 and n=1 exactly: H_n=1 and the
support is empty at those anchors. This theorem concerns prime support,
not the multiplicities of primes in H_n.

## 5. Relation to the existing primorial universe

centeredOddGapProduct_primeFactors proves:

    primeFactors(H_n) = (primeScalesUpTo(2*n-1)).erase 2.

centeredOddGapProduct_radical_eq_primorial proves the product of those distinct
prime factors equals finitePrimeBasisProduct of that existing filtered prime
basis. No division by 2 and no second primorial framework is needed.

H_n itself usually contains prime powers and is not the bounded primorial.
Only its distinct-prime product is identified with the odd bounded primorial.

## 6. What the visible norm divisor measures

The exact definition is A_n=gcd(N_n,H_n), a positive divisor of N_n.
For prime p:

    p divides A_n
      iff p divides N_n and p!=2 and p<2*n
      iff some j<n has p dividing gcd(L(n,j),R(n,j)).

Thus it compresses exactly the prime support union of all local fold gcds,
including fresh primes above n. It also retains capped multiplicity, rather
than being a squarefree radical. Its prime-factorization coordinate is given
in answer9.

old_prime_dvd_centeredNormGapGcd_iff proves:

    p<=n and p divides A_n
      iff centeredCommonSupportIndices n p is nonempty.

fresh_prime_centered_pair_packet supplies a local pair witness for every
visible fresh prime, excludes membership in either bounded old support, and
retains mod4 and width bounds. The n=3 fresh5 and n=6 old5 cases are both
included. Restricting visibility prematurely to p<=n would lose the n=3
composite detector.

## 7. Exact positive-anchor composite detector

centeredFoldNorm_prime_iff_normGapGcd_eq_one proves for n>0:

    N_n is prime iff A_n=1.

Together with centeredNormGapGcd_eq_one_iff_all_pairs it proves:

    N_n is prime iff every fold pair has gcd1.

The forward direction uses N_n>=2*n: a prime N_n cannot occur in odd-gap
support below 2*n. For the converse, n=1 gives prime5 directly. At n>=2,
if N_n is composite, its least prime factor p satisfies p^2<=N_n<(2*n)^2,
so p<2*n. The odd norm excludes p=2, hence p occurs in H_n and contradicts
A_n=1. The needed small-factor API is Nat.minFac_sq_le_self.

The only excluded anchor is n=0: N_0=1 is not prime but A_0=1. That exception
is kernel-calibrated. The kernel checks also cover N_1=5, N_2=13, N_3=25 with
A_3=5, N_6=85 with A_6=5, and prime N_297=177013 with A_297=1. The 297
primality certificate is rechecked by Lean; it is not inferred from Python.

This detects primality of the norm polynomial. It does not assert that an
arbitrary anchor has a prime norm or a prime in its square shell.

## 8. Exact product of local gcds

The definition is:

    P_n = product over j<n of gcd(L(n,j),R(n,j)).

centeredFoldGcdProduct_eq_norm_gaps rewrites it exactly as the product of
gcd(N_n,2*j+1). Safe divisibility bounds are kernel-proved:

    P_n divides N_n^n; P_n divides H_n; P_n>0.

prime_dvd_centeredFoldGcdProduct_iff proves P_n and A_n have identical prime
support. They also have value1 at exactly the same anchors. In particular
P_297=1 follows symbolically from norm primality, without expanding a huge
product. Their numerical values are not asserted equal.

## 9. Exact valuation identities

Factorization coordinates are proved for every natural p:

    factorization(P_n)(p)
      = sum over j<n of min(factorization(N_n)(p), factorization(G_j)(p)).

    factorization(A_n)(p)
      = min(factorization(N_n)(p), factorization(H_n)(p)).

    factorization(H_n)(p)
      = sum over j<n of factorization(G_j)(p).

All factors are nonzero: the norm, gaps, both aggregate objects and odd-gap
product are positive. Nat.factorization_prod_apply and factorization_gcd
therefore apply with their explicit nonzero hypotheses.

For prime p, Nat.factorization_def gives the requested padicValNat versions:

    v_p(P_n) = sum over j<n of min(v_p(N_n),v_p(G_j)).
    v_p(A_n) = min(v_p(N_n), sum over j<n of v_p(G_j)).

No convention about the valuation of zero is silently used.

The optional odd-product valuation phase also closes. Existing double
factorial/factorial splitting yields:

    (2*n)! = (2^n*n!)*H_n.
    v_p(H_n) = v_p((2*n)!)-(n*v_p(2)+v_p(n!)).

For odd prime p this simplifies to v_p((2*n)!)-v_p(n!). The factorization
coordinate version is also proved, so no new factorial theory or analytic
Wallis argument is needed.

## 10. Support aggregate versus multiplicity aggregate

A_n caps each prime's total gap multiplicity by the norm multiplicity once.
P_n caps independently at every pair and then sums across pairs. It can retain
many incidences of a norm prime of exponent1.

The first bounded value difference is n=8:

    N_8=145; A_8=5; P_8=25.
    v_5(A_8)=1; v_5(P_8)=2.

This difference and both valuations are kernel-checked. At n=21, A_n=925
whereas P_n=115625=5^5*37. The repeated local gcd25 contributes two units of
5-valuation at one pair, and the old prime5 also occurs at other pair indices.
Support compression preserves fresh primes but must not be presented as
preserving the incidence valuation unchanged.

## 11. Clean fourth cyclotomic interpretation

The existing CFBRC shifted homogeneous evaluator is reused. The shape
Phi_4(X)=X^2+1 follows from Mathlib's prime-power geometric-sum theorem; there
was no imported Polynomial.cyclotomic_four convenience lemma.

centeredFoldNorm_eq_cyclotomic_four and its inverse orientation prove:

    N_n = cyclotomicShiftedEval 4 1 n
        = cyclotomicShiftedEval 4 (-1) (n+1), as integers.

These evaluate the homogeneous polynomial a^2+b^2 at consecutive coordinates.
Its index is4 and its polynomial degree is2.

For every prime p dividing N_n, the existing denominator theorem excludes
p dividing n+1. prime_dvd_centeredFoldNorm_ratio_sq proves the square of
primeRatio p n (n+1), representing n/(n+1), is -1 in ZMod p.
prime_dvd_centeredFoldNorm_order_four proves primeOrder p n (n+1)=4 using the
existing homogeneous address equivalence. Oddness excludes p dividing4.
No cyclotomic-field extension was introduced.

This supplies an exact order-four address, not a primitive first-appearance
theorem across the varying anchor n. The prime5 reappears visibly at n=3 and
n=6; nonconsecutive_prime_reappears kernel-checks this recurrence. Consecutive
coprimality is not pairwise coprimality of the sequence.

## 12. Consecutive aggregate separation

Both statements are proved for every natural n:

    Coprime(A_n,A_(n+1)).
    Coprime(P_n,P_(n+1)).

The first follows because each A divides its norm. The second follows because
P_n divides N_n^n, P_(n+1) divides N_(n+1)^(n+1), and powers of the coprime
consecutive norms remain coprime. This separates all common-fold multiplicity
across two consecutive shells, not just one chosen trajectory or old support.
It does not itself forbid full cover with changing individual support.

## 13. Skeptical full-cover relevance and finite diagnostics

No positive full-cover shell was observed in the finite range. Consequently
this scan cannot refute a positive-anchor conditional theorem of the form
"full cover implies A_n>1", "full cover implies a nontrivial fold gcd", or
"full cover implies an old common-support pair". No such new positive-anchor
condition was proved either. Logical independence from hypothetical full cover
has not been established.

The unqualified implication over all natural n is false at n=0: the empty
shell is fully covered vacuously, while A_0=P_0=1. The regression
zero_full_cover_counterexample checks this exact exception. It is not a
nontrivial positive-shell counterexample.

Covered pair families can have every fold gcd equal to1. At n=4, all four
fold gcds are1 and the pair20/21 is covered. At n=5, all five fold gcds are1,
and the three pairs with indices2,3,4 are entirely covered. The other two
pairs have escaping seats. These are covered subfamilies, not fully covered
positive shells. The corresponding kernel regressions are
covered_coprime_four and covered_coprime_five_family.
prime_norm_does_not_force_full_cover also kernel-proves prime N_5 and A_5=1
with failure of full coverage. Thus gcd-one does not imply full coverage.
The reverse conditional at positive anchors remains undecided here.

The present norm/gap objects and their exact formulas do not mention coverage.
That separation of definitions is not a proof of logical independence.
The existing full-cover packet requires prime support on individual complete
points; it need not require common support within a pair. No aggregate budget
was proved incompatible with full cover, and no primitive-prime provider was
obtained from these identities.

Diagnostics cover every natural anchor0..300 and extra1031. They use exact
point gcds and factorizations; huge odd products and huge local products are
represented by support and valuation maps. The inherited017 colors determine
coverage only; current gcd and valuation statistics are computed independently.
For n>=2, U denotes the escaping-seat count; n=0,1 have separate boundary
records rather than extrapolating that parity convention.

| n | N_n | A_n | pairs with gcd>1 | visible old primes | visible fresh primes | P_n factors | U |
|---|---|---|---|---|---|---|---|
| 3 | 25 | 5 | 1 | none | 5 | 5 | 2 |
| 5 | 61 | 1 | 0 | none | none | 1 | 2 |
| 6 | 85 | 5 | 1 | 5 | none | 5 | 4 |
| 8 | 145 | 5 | 2 | 5 | none | 5^2 | 4 |
| 11 | 265 | 5 | 2 | 5 | none | 5^2 | 4 |
| 19 | 761 | 1 | 0 | none | none | 1 | 6 |
| 21 | 925 | 925 | 5 | 5 | 37 | 5^5*37 | 7 |
| 29 | 1741 | 1 | 0 | none | none | 1 | 8 |
| 297 | 177013 | 1 | 0 | none | none | 1 | 45 |
| 1031 | 2127985 | 305 | 220 | 5,61 | none | 5^206*61^17 | 160 |

Primality/factorization diagnostics, odd-product support and valuations, local
gcd records and covered coprime subfamilies are retained in
[discovery-018.json](evidence/MANIFEST.md#log-c82016422f1c5ab5).
The 1031 norm factorization is5*61*6977; prime6977 is invisible because it
exceeds2*n. Its 223 prime incidences come from206 plus17, while the pair union
has220 members because three pairs have both common primes. None of these
large census values is silently promoted to a kernel theorem: visible1031
checks the two prime divisibilities and exclusion of6977 without evaluating
huge products. The old017 scalar support counts206 and17 remain kernel results.

There is no exact U law in these statistics. For example U=2 at n=3 and n=5,
but A_n is5 and1 respectively; A_n=1 at n=5,19,29,297 accompanies U=2,6,8,45.
These finite witnesses rule out treating A as a deterministic U classifier
in the scanned data. No asymptotic correlation or positive full-cover
obstruction is inferred.

## 14. Single next contract and implementation proposal

The next contract is the exact prime-power floor compression:

    centeredFoldGcdProduct_padicVal_eq_primePowerFloorSum

For prime p!=2 and every natural n, propose:

    v_p(P_n)
      = sum over k in Icc(1,v_p(N_n)) of
          floor((n+(p^k-1)/2)/p^k).

This is proposed, not implemented or counted among the current results.
It would remove the per-seat valuation sum while preserving repeated-prime
and fresh-prime multiplicity. It does not assume or conclude failure of full
coverage and does not disguise Legendre as a provider.

Implement it in CenteredFoldGcdAggregate. Rewrite each min valuation as the
finite count of positive k up to v_p(N_n) whose p^k divides G_j. Exchange the
two finite sums. For each odd modulus p^k, prove the address count by the same
half-residue progression and range bijection used in017 for prime p; oddness
and positivity suffice, so no false assertion of primality of p^k is needed.
The floor count then gives the displayed formula. Reuse factorization/padic
conventions and keep the zero/empty sum explicit.

Acceptance examples should include n=0, gap-one anchors, the n=3 fresh5
branch, n=8 with two5 incidences, and n=21 where the p=5 floor terms are4 and1,
adding to5. The n=1031 p=5 and p=61 cases should use symbolic formulas rather
than enormous products. Apply complete axiom and facade validation before
using the result as a counted input to an existing cover-incidence interface.
No primitive first-appearance terminology is justified by the current results.

Outcome B - FOLD GCD AGGREGATE YIELDS A NEW PRIMORIAL OR CYCLOTOMIC BRIDGE
