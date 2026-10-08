# Findings 030 - Independent envelope without a strict gain

## Exact identification

Q counts the old large prime carry labels, each once with log(p). A window pair
has k=base/p+1, so the prime carriers of distinct cofactor windows are disjoint.
The next-multiple packet gives the target p*k. Target injection also follows
from the existing 028 distinct-large-base exclusion and the 029 target theorem.
Index uniqueness supplies the bridge; it is not a reduction in log weight.

## Bound selected

Set A=max(base/k,width), B=top/k, C=B-A in natural subtraction. The quotient
length estimate gives C<p for every window prime. Since A<p<=B as well,
Nat.Prime.dvd_choose shows p divides choose(B,C). Distinct prime products divide
the coefficient and are no larger than it. Logarithms give the independent sum
U(n)=sum over k of log(choose(B,C)). When B<A, C=0 and the term is log(1)=0.

The final bound G takes the smaller coefficient in each window: choose(B,C)
or max(1,B)^J, where J=((B+1)/2)-((A+1)/2). The odd cardinal bound is proved
by the half-interval injection p mapped to p/2. Hence Q<=G<=U. The combined G
matches the odd-only cap numerically at all retained anchors;
no additional minimum gain or global equality is inferred. Both estimates
are independent of carry-event membership; no optimality claim is made.

The estimates overcount prime factors outside the actual window and
composite-only windows. The exact ledger excess is G-Q, always nonnegative.
The exact higher-correction consumer is therefore at least as demanding as
the original ledger consumer.

## Diagnostic decisions

An independent sieve reconstructs all quotient-window pairs for n=3..5000.
They equal the hashed 028 singleton labels. Prime and target projections are
injective throughout this finite range. Floating binomial log estimates use
lgamma; weights and margins are not proof premises.

The binomial envelope passes the exact-higher consumer at 3,4,5,6 only in this
range. The parity envelope and the final combined G pass 3,4,5,6,8. Both fail
at 7, which is the first admissible failure but not a monotone threshold. The
log-log replacement passes 3,4 for U and 3,4,6 for G. The all-integer cardinal
envelope is looser. The additional passing anchor 8 motivated formalizing the
combined bound instead of stopping at the binomial-only candidate.

The n=4 strict slack and the n=7 failure are preserved by kernel-checked
integer products and symbolic log comparisons; the passing margins at 3..6
and 8 are kernel checked as well. The numerical search does not establish any
universal failure threshold or improvement over the 029 fiber budget.

## Natural frontier

A further small-prime wheel filter can remove the composite-only window (14,15]
at n=7, but a fixed local filter is not itself a general short-window estimate.
A useful next research target is a rigorously controlled weighted sieve error
summed over all cofactor windows. Any such proposal must control the accumulated
window errors independently of the old carry inventory and preserve the small,
repeated-power, and higher residuals. No subsequent checkpoint is predesigned.

## Final validation

Focused, facade, root and complete public axiom builds passed with two Lean
threads. Kernel checks fix first strict slack at 4 and first consumer failure
at 7, with all earlier admissible margins checked. All 31 public declarations
have only standard logical axioms and no sorryAx dependencies. Root warnings
are inherited and documented separately. Outcome B: independent geometric
bound, exact ledger bridge, and no universal strict gain.
