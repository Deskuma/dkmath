# FLT7TC-005R59 — Current cyclotomic constructor and exact Galois phase transport

## Scope

R59 extends the neutral R58 address/phase layer to the current common-prime
packet.  The construction is kept separate from the historical signed-root
terminal packets.  The explicit C>1 common-prime branch remains the scope;
this report does not claim FLT7 closure.

## Incremental ledger

| instruction/source/API inspection | complete |
| report scaffold | complete |
| current quotient-side residue packet | complete |
| primitive seventh-root ratio and phase-normalized address | complete |
| degree-six current kernel pair | complete |
| fixed-ZMod oriented gap-prime transport | complete |
| neutral fourteen-power and coefficient-ratio lemmas | complete |
| scratch checks, focused build, and audits | complete |

## Implemented APIs

`SevenRealCubicCurrentCommonPrimePacket.lean` now constructs the current
quotient-side packet with the actual prime ideal `Q`, its maximal/prime and
lying-over data, the residue-field equivalence to `ZMod q`, the evaluation
formula, quotient-root zero, and the two required nonzero orbit values.  The
same packet constructs the primitive seventh-root ratio and derives
`tau ^ 7 = 1`, `tau ≠ 1`, `orderOf tau = 7`, and `q % 7 = 1` in the forward
direction.

The current cyclotomic address now exposes maximality and contraction facts
for the current and conjugate degree-six kernels.  The carrier
`zeta - ofReal ratio.val.val` proves that the two kernels are distinct from
the current ratio and its inverse; no historical signed-root packet is used.

`SevenRealCubicCurrentOrientedGapTransport.lean` adds the independent
oriented gap-prime packet.  It stores `P`, its degree-one residue-field
equivalence, and `f0`, with the exact gap-root zero pattern.  Its `f1` and
`f2` maps are defined by the inverse fixed `ZMod` rotations, and the
rotation identities and transported zero/nonzero facts are kernel checked.
The quotient-side and oriented evaluations remain separate.

`SevenRealCubicCurrentCyclotomicFourteen.lean` contains the three neutral
fourteen-power zero-index lemmas.  `SevenRealCubicCurrentCoefficientRatios.lean`
contains the three unit coefficient ratios and their product `-1`.

## Verification

The following focused checks passed sequentially:

```text
lake build DkMath.FLT.Seven.SevenRealCubicCurrentCommonPrimePacket
lake build DkMath.FLT.Seven.SevenRealCubicCurrentCyclotomicFourteen
lake build DkMath.FLT.Seven.SevenRealCubicCurrentCoefficientRatios
lake build DkMath.FLT.Seven.SevenRealCubicCurrentOrientedGapTransport
lake env lean docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/scratch-065-current-constructor.lean
lake build DkMath.FLT.Seven
```

The scratch `#print axioms` audit reports only the expected
`propext`, `Classical.choice`, and `Quot.sound` dependencies for the
finite-field/ideal constructions; the generic coefficient-ratio product
reports `propext` only.  The R59 files and scratch contain no prohibited
implementation marker or native-evaluation construct.

The decisive identification of the quotient-side packet with the oriented
gap-prime packet, the I1/I2 transport-product adjudication, and all resulting
mod-28 or terminal FLT7 conclusions remain outside this implementation.

## Boundary

Do not identify the quotient-side and oriented gap-prime evaluations unless a
kernel theorem proves that identification.  No mod-28 claim is made from
`q % 7 = 1` alone, and no historical terminal contradiction is imported.
